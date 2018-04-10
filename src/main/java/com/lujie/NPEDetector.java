package com.lujie;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Collection;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.Map;
import java.util.TreeSet;
import java.util.Map.Entry;
import java.util.Properties;
import java.util.Set;

import com.ibm.wala.cfg.cdg.ControlDependenceGraph;
import com.ibm.wala.cfg.exc.intra.SSACFGNullPointerAnalysis;
import com.ibm.wala.classLoader.CallSiteReference;
import com.ibm.wala.classLoader.IClass;
import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.ipa.callgraph.AnalysisCacheImpl;
import com.ibm.wala.ipa.callgraph.AnalysisOptions;
import com.ibm.wala.ipa.callgraph.AnalysisScope;
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.CallGraph;
import com.ibm.wala.ipa.callgraph.CallGraphBuilder;
import com.ibm.wala.ipa.callgraph.CallGraphBuilderCancelException;
import com.ibm.wala.ipa.callgraph.CallGraphStats;
import com.ibm.wala.ipa.callgraph.Entrypoint;
import com.ibm.wala.ipa.callgraph.impl.AllApplicationEntrypoints;
import com.ibm.wala.ipa.callgraph.impl.DefaultEntrypoint;
import com.ibm.wala.ipa.cfg.ExceptionPrunedCFG;
import com.ibm.wala.ipa.cfg.PrunedCFG;
import com.ibm.wala.ipa.cha.ClassHierarchy;
import com.ibm.wala.ipa.cha.ClassHierarchyException;
import com.ibm.wala.ipa.cha.ClassHierarchyFactory;
import com.ibm.wala.properties.WalaProperties;
import com.ibm.wala.shrikeBT.ArrayLengthInstruction;
import com.ibm.wala.ssa.DefUse;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.ISSABasicBlock;
import com.ibm.wala.ssa.SSAAbstractInvokeInstruction;
import com.ibm.wala.ssa.SSAArrayLengthInstruction;
import com.ibm.wala.ssa.SSAConditionalBranchInstruction;
import com.ibm.wala.ssa.SSAFieldAccessInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAPhiInstruction;
import com.ibm.wala.ssa.SSAReturnInstruction;
import com.ibm.wala.ssa.SymbolTable;
import com.ibm.wala.util.WalaException;
import com.ibm.wala.util.collections.HashMapFactory;
import com.ibm.wala.util.collections.HashSetFactory;
import com.ibm.wala.util.collections.Pair;
import com.ibm.wala.util.config.AnalysisScopeReader;
import com.ibm.wala.util.intset.IntSet;
import com.ibm.wala.util.io.FileProvider;
import com.ibm.wala.util.io.FileUtil;
import com.sun.xml.internal.bind.v2.TODO;

/**
 * 
 * */
public class NPEDetector {
 * NPE分析工具的入口类
 * @author lujie
 */
public class NPEDectetor {
    private static final Logger logger = Logger.getLogger(NPEDectetor.class);
    /**
     * 分析的项目所在的目录路径
     */
	private String jarDir = null;
    /**
     * 函数调用关系图
     */
	private CallGraph callGraph = null;
    /**
     * 依据项目的大小，选择是否需要精确分析main
     * 默认为false
     */
	private boolean mainEntrypoints = false;
	private boolean debug = false;
    /**
     * 设置100000000为大项目的阈值
     */
	private static long CUTOFF_SIZE = 100000000;
	private boolean simpleAnalysis = true;
	private String outputFile = null;
    /**
     * 类的层次结构
     */
	private ClassHierarchy cha = null;
	private Map<CGNode, CGNode> trasnCalleeToRootCallee;
    /**
     * 存储节点分数的map
     */
	private Map<CGNode, Integer> checkedCalleeCount;
    /**
     *
     */
	private Map<CGNode, CGNode> transCalleeToRootCallee;

	public NPEDetector() {
		trasnCalleeToRootCallee = HashMapFactory.make();
	}

	public static void main(String[] args) throws IOException,
			ClassHierarchyException, IllegalArgumentException,
			CallGraphBuilderCancelException {
		NPEDetector dectetor = new NPEDetector();
		dectetor.checkParameter();
		dectetor.makeCallGraph();
		System.out.println("start to find potential NPE");
		Collection<CGNode> returnNullNodes = dectetor.findAllReturnNullNode();
		Map<CGNode, Set<CGNode>> calleeMap2Callers = dectetor
				.findCallers(returnNullNodes);
		ControldependencyAnalysis controldependencyAnalysis = dectetor
				.getControlDependencyAnalysis();

		Map<CGNode, Set<CGNode>> noNEChekerCalleeMap2Callers = controldependencyAnalysis
				.analysis(calleeMap2Callers);
		Set<ScoreNode> scoreNodes = dectetor.buildScoreSet(
				noNEChekerCalleeMap2Callers,
				controldependencyAnalysis.getCheckedCalleeCount());
		dectetor.dumpResult(scoreNodes);
	}

	private ControldependencyAnalysis getControlDependencyAnalysis() {
		if (simpleAnalysis) {
			return new SimpleControldependencyAnalysis(callGraph,
					trasnCalleeToRootCallee);
		} else {
			return new ComplexControldependencyAnalysis(callGraph,
					trasnCalleeToRootCallee);
		}
		logger.info("test log...");
	    NPEDectetor dectetor = new NPEDectetor();
	    try {
            //  1 检查JER version
		dectetor.checkJREVersion();
            //  2 检查参数是否合法
            dectetor.checkParameter(args);
            //  3 创建函数调用关系图
            dectetor.makeCallGraph();
            logger.info("starting to find potential NPE");
            //  4 找出所有返回null的函数集合
            Collection<CGNode> returnNullNodes = dectetor.findAllReturnNullNode();
            //  5 找出callee与caller之间的对应关系
            Map<CGNode, Set<CGNode>> calleeMap2Callers = dectetor
                    .findCallers(returnNullNodes);
            //  6
            Map<Pair<CGNode, CGNode>, Set<Pair<CGNode, SSAInstruction>>> ssaMayReferenceNull = dectetor
                    .findSSAMayReferenceNull(calleeMap2Callers);
            //  7 过滤
            dectetor.filterByIfNENull(ssaMayReferenceNull);
            //  8 按分数排序节点
            Set<ScoreNode> scoreNodes = dectetor.buildScoreSet(ssaMayReferenceNull);
            //  9 输出结果
            dectetor.dumpResult(args[1], scoreNodes);
        } catch (Exception e) {
            logger.error(e);
        }

	}

	private void dumpResult(Set<ScoreNode> scoreNodes) {
		File file = new File(outputFile);
		FileWriter writer = null;
		try {
			writer = new FileWriter(file);
			for (ScoreNode scoreNode : scoreNodes) {
				StringBuilder sb = new StringBuilder();
				sb.append(Util.getSimpleMethodToString(scoreNode.node));
				for (CGNode caller : scoreNode.callers) {
					sb.append(" ");
					sb.append(Util.getSimpleMethodToString(caller));
				}
				sb.append("\n");
				writer.write(sb.toString());
			}
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} finally {
			if (writer != null) {
				try {
					writer.close();
				} catch (IOException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			}
		}
	}

    /**
     *
     * @param map
     * @return
     */
	private Set<ScoreNode> buildScoreSet(
			Map<CGNode, Set<CGNode>> calleeMap2Callers,
			Map<CGNode, Integer> checkedCalleeCount) {
		Set<ScoreNode> ret = new TreeSet<ScoreNode>();
		for (Entry<CGNode, Set<CGNode>> entry : calleeMap2Callers.entrySet()) {
			ScoreNode scoreNode = new ScoreNode();
			scoreNode.node = entry.getKey();
			scoreNode.callers = entry.getValue();
			scoreNode.score -= entry.getValue().size();
			Integer score = checkedCalleeCount.get(entry.getKey());
			if (score != null) {
				scoreNode.score += score * 10;
			}
			ret.add(scoreNode);
		}
		return ret;
	}

	private void checkParameter() {
		try {

			// check jre
			Properties p = WalaProperties.loadProperties();
			String javaHome = p.getProperty(WalaProperties.J2SE_DIR);
			if (!javaHome.contains("1.7")) {
				Util.exitWithErrorMessage("check your javahome wrong jdk version , must be 1.7");
			}
			// check jardir
			jarDir = p.getProperty("jardir");
			if (jarDir == null) {
				Util.exitWithErrorMessage("please configure your jardir");
			}
			// user may mistake leave a blank space end of the path
			jarDir.replaceAll(" ", "");

			outputFile = p.getProperty("outputfile");
			if (outputFile == null) {
				Util.exitWithErrorMessage("please configure your outputfile");
			}
			outputFile.replaceAll(" ", "");
			// check debug
			String debugString = p.getProperty("debug");
			if (debugString != null && debugString.equals("true")) {
				debug = true;
			}
			// check cda
			String cda = p.getProperty("cda");
			if (cda != null && cda.equals("complex")) {
				simpleAnalysis = false;
			}
		} catch (WalaException e) {
			e.printStackTrace();
			System.exit(1);
		}
	}

    /**
     * 构建函数调用关系图
     * @throws IOException
     * @throws ClassHierarchyException
     * @throws IllegalArgumentException
     * @throws CallGraphBuilderCancelException
     */
	private void makeCallGraph() throws IOException, ClassHierarchyException,
			IllegalArgumentException, CallGraphBuilderCancelException {
		long start_time = System.currentTimeMillis();
		System.out.println("start to make call graph");

		FileProvider fileProvider = new FileProvider();
		// 排除一些文件
		File exclusionsFile = fileProvider
				.getFile("Java60RegressionExclusions.txt");

		String jarFiles = findJarFiles(new String[] { jarDir });
        // 会非法参数异常
		AnalysisScope scope = AnalysisScopeReader.makeJavaBinaryAnalysisScope(
				jarFiles, exclusionsFile);
        // 存储类的层次结构信息
		cha = ClassHierarchyFactory.make(scope);

		Iterable<Entrypoint> entryPointIterator = null;
		if (debug) {
			entryPointIterator = addSpecialEntryPoint();
		} else if (mainEntrypoints) {
			entryPointIterator = com.ibm.wala.ipa.callgraph.impl.Util

		if (mainEntrypoints) {
		    // 指定main方法分析
            entryPointIterator = com.ibm.wala.ipa.callgraph.impl.Util
					.makeMainEntrypoints(scope, cha);
		} else {
		    // 精确分析
			entryPointIterator = new AllApplicationEntrypoints(scope, cha);
		}
        //
		AnalysisOptions options = new AnalysisOptions(scope, entryPointIterator);
		// 0-CFA is faster and more precise
        //
        CallGraphBuilder<?> builder = com.ibm.wala.ipa.callgraph.impl.Util
				.makeZeroCFABuilder(options, new AnalysisCacheImpl(), cha,
						scope);
        //
		callGraph = builder.makeCallGraph(options, null);
		// logger info
		System.out.println(CallGraphStats.getStats(callGraph));
		System.out.println("Time spent ont building CHA and CG:"
				+ (System.currentTimeMillis() - start_time) + "ms");
	}

	private String findJarFiles(String[] directories) {
	    // 所分析的项目的大小
		long size = 0;
        StringBuffer result = new StringBuffer();
		for (int i = 0; i < directories.length; i++) {
			for (File f : FileUtil.listFiles(directories[i], ".*\\.jar", true)) {
                result.append(f.getAbsolutePath());
                result.append(File.pathSeparator);
				size += f.length();
			}
		}
        // logger size
		if (size > CUTOFF_SIZE) {
		    //logger  MainApplciationEntryPoint
			// 设置入口方法点
			mainEntrypoints = true;
		} else {
			message.append("AllApplciationEntryPoint");
		}else{
            // 不设置入口方法点
            // logger AllApplciationEntryPoint
		}
		if (!debug) {
			System.out.println(message);
		}
		return composeString(result);
		return result.substring(0, result.length()-1).toString();
	}

	private String composeString(Collection<String> s) {
		StringBuffer result = new StringBuffer();
		Iterator<String> it = s.iterator();
		for (int i = 0; i < s.size() - 1; i++) {
			result.append(it.next());
			result.append(File.pathSeparator);
		}
		result.append(it.next());
		return result.toString();
	}

	// 检查JRE版本
	private void checkJREVersion() {
		try {
			Properties p = WalaProperties.loadProperties();
			String javaHome = p.getProperty(WalaProperties.J2SE_DIR);
			if (!javaHome.contains("1.7")) {
			    // logger error
				System.err
						.println("check your javahome wrong jdk version , must be 1.7");
			}
		} catch (WalaException e) {
		    // logger.error
			e.printStackTrace();
			System.exit(1);
		}
	}

    /**
     *
     * @return
     */
	private Collection<CGNode> findAllReturnNullNode() {
		Set<CGNode> returnNullNodes = HashSetFactory.make();
		for (CGNode node : callGraph) {
			/* debug point for check special method */
			if (node.toString().contains("BinaryInputArchive")
					&& node.toString().contains("readBuffer")) {
				System.out.print("");
			}
			if (Util.isApplicationNode(node) && isReturnNullNode(node)) {
				returnNullNodes.add(node);
			}
		}
		return returnNullNodes;
	}

    /**
     *
     * @param node
     * @return
     */
	private boolean isReturnNullNode(CGNode node) {
		IR ir = node.getIR();
		if (ir == null) {
            return false;
        }
		for (SSAInstruction ins : ir.getInstructions()) {
			if (ins instanceof SSAReturnInstruction
					&& isReturnNullInstruction((SSAReturnInstruction) ins, node)) {
				return true;
			}
		}
		return false;
	}

    /**
     *
     * @param returnIns
     * @param node
     * @return
     */
	private boolean isReturnNullInstruction(SSAReturnInstruction returnIns,
			CGNode node) {
		IR ir = node.getIR();
		DefUse defUse = node.getDU();
		SymbolTable symbolTable = ir.getSymbolTable();
		int use = returnIns.getUse(0);
		if (use < 0) {
			return false;
		}
		// case 0: directly "return null"
		if (symbolTable.isNullConstant(use)) {
			return true;
		}
		// case 1: phi v0 = v1:#str, v2:#null,...
		// TODO handle that v1 is still def by SSAPhiInstruction
		SSAInstruction defIns = defUse.getDef(use);
		if (defIns instanceof SSAPhiInstruction) {
			for (int i = 0; i < defIns.getNumberOfUses(); i++) {
				use = defIns.getUse(0);
				if (use != -1 && symbolTable.isNullConstant(use)) {
					return true;
				}
			}
		}
		// case n:?, maybe
		return false;
	}

    /**
     * 找一个callee对应的所有caller
     * @param rootCallee
     * @param transcallee
     * @param checkedNode
     * @return
     */
	private Collection<Pair<CGNode, CGNode>> findCaller(CGNode rootCallee,
			CGNode transcallee, Collection<CGNode> checkedNode) {
		Set<Pair<CGNode, CGNode>> ret = HashSetFactory.make();
		if (checkedNode.contains(transcallee)) {
            return ret;
        }
		checkedNode.add(transcallee);
		Iterator<CGNode> callerIterator = callGraph.getPredNodes(transcallee);
		while (callerIterator.hasNext()) {
			CGNode caller = callerIterator.next();
			if (caller.equals(callGraph.getFakeRootNode())
					|| !Util.isApplicationNode(caller)) {
				continue;
			}
			IR ir = caller.getIR();
			DefUse du = caller.getDU();
			Iterator<CallSiteReference> callSiteIterator = callGraph
					.getPossibleSites(caller, transcallee);
			while (callSiteIterator.hasNext()) {
				CallSiteReference callSite = callSiteIterator.next();
				SSAAbstractInvokeInstruction[] ssaAbstractInvokeInstructions = ir
						.getCalls(callSite);
				for (SSAAbstractInvokeInstruction ssaAbstractInvokeInstruction : ssaAbstractInvokeInstructions) {
					int def = ssaAbstractInvokeInstruction.getDef();
					Iterator<SSAInstruction> useIterator = du.getUses(def);
					if (useIterator.hasNext()) {
						SSAInstruction useInstruction = useIterator.next();
						if (!(useInstruction instanceof SSAReturnInstruction)) {
							ret.add(Pair.make(caller, transcallee));
                            transCalleeToRootCallee
									.put(transcallee, rootCallee);
							continue;
						}
						ret.addAll(findCaller(rootCallee, caller, checkedNode));
					}
				}
			}
		}
		return ret;
	}

    /**
     * 找出callee的所有caller
     * @param returnNullNodes 返回null的函数集合
     * @return callee与caller的对应关系
     */
	private Map<CGNode, Set<CGNode>> findCallers(
			Collection<CGNode> returnNullNodes) {
		Map<CGNode, Set<CGNode>> calleeMapCallers = HashMapFactory.make();
		for (CGNode returnNullNode : returnNullNodes) {
			/* debug point for check special method */
			if (returnNullNode.toString().contains("SecurityUtils")
					&& returnNullNode.toString().contains("createSaslClient")) {
				System.out.print("");
			}
			Collection<Pair<CGNode, CGNode>> callerAndCallees = this
					.findCaller(returnNullNode, returnNullNode,
							new HashSet<CGNode>());
			for (Pair<CGNode, CGNode> pair : callerAndCallees) {
				if (calleeMapCallers.get(pair.snd) == null) {
					calleeMapCallers.put(pair.snd, new HashSet<CGNode>());
				}
				calleeMapCallers.get(pair.snd).add(pair.fst);
			}
		}
		return calleeMapCallers;
	}

	private Iterable<Entrypoint> addSpecialEntryPoint() {
		final Set<Entrypoint> entrypoints = new HashSet<Entrypoint>();
		for (IClass cls : cha) {
			if (cls.getName().toString().endsWith("FsDatasetImpl")) {
				for (IMethod method : cls.getAllMethods()) {
					entrypoints.add(new DefaultEntrypoint(method, cha));
				}
			}
		}
		return new Iterable<Entrypoint>() {
    /**
     *
     * @param calleeMapCallers
     * @return
     */
	private Map<Pair<CGNode, CGNode>, Set<Pair<CGNode, SSAInstruction>>> findSSAMayReferenceNull(
			Map<CGNode, Set<CGNode>> calleeMapCallers) {
		Map<Pair<CGNode, CGNode>, Set<Pair<CGNode, SSAInstruction>>> result = HashMapFactory
				.make();
		for (Entry<CGNode, Set<CGNode>> entry : calleeMapCallers.entrySet()) {
			CGNode callee = entry.getKey();
			/*debug point for check special method*/
			if (callee.toString().contains("BinaryInputArchive")
					&& callee.toString().contains("readBuffer")) {
				System.out.print("");
			}
			Set<CGNode> callers = entry.getValue();
			for (Iterator<CGNode> callerIterator = callers.iterator(); callerIterator
					.hasNext();) {
				CGNode caller = callerIterator.next();
				IR ir = caller.getIR();
				Iterator<CallSiteReference> callSiteIterator = callGraph
						.getPossibleSites(caller, callee);
				Set<Pair<CGNode, SSAInstruction>> refernces = HashSetFactory
						.make();
				while (callSiteIterator.hasNext()) {
					CallSiteReference callSiteReference = callSiteIterator
							.next();
					SSAAbstractInvokeInstruction[] ssaAbstractInvokeInstructions = ir
							.getCalls(callSiteReference);
					for (SSAAbstractInvokeInstruction ssaAbstractInvokeInstruction : ssaAbstractInvokeInstructions) {
						int def = ssaAbstractInvokeInstruction.getDef();
						if (def == -1) {
							continue;
						}
						refernces.addAll(getFinalRefernces(def, caller));
					}
				}
				if (refernces.size() == 0) {
					callerIterator.remove();
				} else {
					result.put(Pair.make(caller, callee), refernces);
				}
			}
		}
		Iterator<Entry<CGNode, Set<CGNode>>> entryIterator = calleeMapCallers
				.entrySet().iterator();
		while (entryIterator.hasNext()) {
			Entry<CGNode, Set<CGNode>> entry = entryIterator.next();
			if (entry.getValue().size() == 0) {
				entryIterator.remove();
			}
		}
		return result;
	}

    /**
     *
     * @param def
     * @param node
     * @return
     */
	private Set<Pair<CGNode, SSAInstruction>> getFinalRefernces(int def,
			CGNode node) {
		Set<Pair<CGNode, SSAInstruction>> refernces = HashSetFactory.make();
		// case 0:def.call()
		DefUse du = node.getDU();
		Iterator<SSAInstruction> usesIterator = du.getUses(def);
		while (usesIterator.hasNext()) {
			SSAInstruction useInstruction = usesIterator.next();
			if (useInstruction instanceof SSAAbstractInvokeInstruction) {
				if (!((SSAAbstractInvokeInstruction) useInstruction).isStatic()) {
					// case0 : ret = methodReturnNull();ret.foo();
					if (def == useInstruction.getUse(0)) {
						refernces.add(Pair.make(node, useInstruction));
					} else {
						// TODO case1 : ret = methodReturnNull();this.foo(ret);
					}
				} else {
					// TODO case2 : ret = methodReturnNull();staticfoo(ret);
				}
			} else if (useInstruction instanceof SSAFieldAccessInstruction) {
				// case3 : ret = methodReturnNull();ret.a = 1;1==ret.a
				if (def == useInstruction.getUse(0)) {
					refernces.add(Pair.make(node, useInstruction));
				} else {
					// TODO case3 : ret = methodReturnNull();this.a = ret;
				}
			} else if (useInstruction instanceof SSAArrayLengthInstruction) {
				// case3 : ret = methodReturnNull();ret.a = 1;1==ret.a
				if (def == useInstruction.getUse(0)) {
					refernces.add(Pair.make(node, useInstruction));
				} else {
					// TODO case3 : ret = methodReturnNull();this.a = ret;
				}
			} else {
				// TODO: such as phi
			}
		}
		return refernces;
	}

	private void filterByIfNENull(
			Map<Pair<CGNode, CGNode>, Set<Pair<CGNode, SSAInstruction>>> map) {
		Iterator<Entry<Pair<CGNode, CGNode>, Set<Pair<CGNode, SSAInstruction>>>> entryIterator = map
				.entrySet().iterator();
		while (entryIterator.hasNext()) {
			Entry<Pair<CGNode, CGNode>, Set<Pair<CGNode, SSAInstruction>>> entry = entryIterator
					.next();
			Iterator<Pair<CGNode, SSAInstruction>> pairIterator = entry
					.getValue().iterator();
			while (pairIterator.hasNext()) {
				Pair<CGNode, SSAInstruction> pair = pairIterator.next();
				if (controlByNENull(pair.fst, pair.snd)) {
					pairIterator.remove();
					Integer cnt = checkedCalleeCount.get(entry.getKey().snd);
					if (cnt == null) {
						cnt = new Integer(0);
					}
					cnt++;
					checkedCalleeCount.put(entry.getKey().snd, cnt);
				}
			}
			if (entry.getValue().size() == 0) {
				entryIterator.remove();
			}
		}
	}

			public Iterator<Entrypoint> iterator() {
				return entrypoints.iterator();
	// need to handle if (x==null) exit;

    /**
     *
     * @param node
     * @param ssaInstruction
     * @return
     */
	private boolean controlByNENull(CGNode node, SSAInstruction ssaInstruction) {
		IR ir = node.getIR();
		PrunedCFG<SSAInstruction, ISSABasicBlock> exceptionPrunedCFG = ExitAndExceptionPrunedCFG
				.make(ir.getControlFlowGraph());
		ControlDependenceGraph<ISSABasicBlock> cdg = new ControlDependenceGraph<ISSABasicBlock>(
				exceptionPrunedCFG);
		ISSABasicBlock bb = ir.getBasicBlockForInstruction(ssaInstruction);
		Set<ISSABasicBlock> preBBs = HashSetFactory.make();
		findPreBB(cdg, preBBs, bb);
		for (ISSABasicBlock preBB : preBBs) {
			for (SSAInstruction controlSSAInstruction : preBB) {
				if (controlSSAInstruction instanceof SSAConditionalBranchInstruction) {
					if (controlSSAInstruction.getNumberOfUses() != 2) {
						continue;
					}
					int use0 = controlSSAInstruction.getUse(0);
					int use1 = controlSSAInstruction.getUse(1);
					if (ir.getSymbolTable().isNullConstant(use0)
							&& use1 == ssaInstruction.getUse(0)) {
						return true;
					}
					if (ir.getSymbolTable().isNullConstant(use1)
							&& use0 == ssaInstruction.getUse(0)) {
						return true;
					}
				}
			}
		};
	}

    /**
     *
     * @param cdg
     * @param preBBs
     * @param bb
     */
	private void findPreBB(ControlDependenceGraph<ISSABasicBlock> cdg,
			Set<ISSABasicBlock> preBBs, ISSABasicBlock bb) {
		Iterator<ISSABasicBlock> preBBIterator = cdg.getPredNodes(bb);
		while (preBBIterator.hasNext()) {
			ISSABasicBlock preBB = preBBIterator.next();
			if (preBBs.contains(preBB)) {
                continue;
            }
			preBBs.add(preBB);
			findPreBB(cdg, preBBs, preBB);
		}
	}
}
