# NPEDectetor
NPEDectetor is designed to find the potential null pointer exception in the systems writen by java(especially for distributed system). 
# Motivation
<div  align="center">    
 <img src="https://github.com/lujiefsi/NPEDectetor/blob/master/hbase-13546.png" width="60%" height="60%" alt="hbase-13546" align=center />
</div>

above figure shows the bug in hbase:

1. HMaster crash.
2. Zookeeper expire the connection, so data related to master is null.
3. Client send http request for get region server status before HMaster retoot
4. After receive the request, RS will get master data from Zookeeper
5.  Due to step 2, RS get null, and refrernce it w/o check it.

We can see that this bug is complex(involed 4 node and one crash event)
but in  fact, develop have considered the master crash situation while parse:
<pre><code>
//callee: parse
public Master parse(byte[] data){
    if (data == null){
        return null;
    }
}
</code></pre>

but in its caller developer does not take null into count:
<pre><code>
//caller getMasterInfoPort
public getMasterInfoPort(byte[] data){
    Master master = parse(getData(false));
    return master.getInfoPort();
}
</code></pre>

This bug shows that NPE happends in corner case but some (callee) developers are wake up this 
case. So we develop NPEDectetor to catch this simpe bug pattern:<font color=red size=4>callee return null, but caller
does not check it.</font>

# Approach
Based on [WALA](https://github.com/wala/WALA),an famous static analysis framework.

    step1 : find all return null method(RNM)

    step2 : find all RNM' caller;

    step3 : find all RNM return value's use instruction.

    step4 : check all use instructions whether controled by check null condition(CNC)

    step5 : Score each callee:CNC numbers * 10 - caller number.

    step6 : Sort all callees and print.
    
In step5, we score each callee based on:(1) if some developerer have consider CNC, but some are not,
we think no CNC developeres are wrong(2)developer may borther massive [CNC](https://stackoverflow.com/questions/271526/avoiding-null-statements/271874#271874)
