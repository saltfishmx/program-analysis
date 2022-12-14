/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.plugin.taint.TaintAnalysiss;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.Map;
import java.util.Set;

public class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;
    private StmtProcessor stmtProcessor;
    private TaintAnalysiss taintAnalysis;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    public AnalysisOptions getOptions() {
        return options;
    }

    public ContextSelector getContextSelector() {
        return contextSelector;
    }

    public CSManager getCSManager() {
        return csManager;
    }

    void solve() {
        initialize();
        analyze();
        taintAnalysis.onFinish();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        taintAnalysis = new TaintAnalysiss(this);
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        if(!callGraph.contains(csMethod)){
            callGraph.addReachableMethod(csMethod);
            IR ir = csMethod.getMethod().getIR();
            ir.forEach(stmt->{
                stmtProcessor = new StmtProcessor(csMethod);
                stmt.accept(stmtProcessor);
                if(stmt instanceof  Invoke){ // handle source
                    Obj taintobj = taintAnalysis.getTaintObj(stmt);
                    if(taintobj!=null){
                        CSObj cto = csManager.getCSObj(contextSelector.getEmptyContext(),taintobj);
                        CSVar cvar = csManager.getCSVar(csMethod.getContext(),((Invoke) stmt).getLValue());
                        workList.addEntry(cvar,PointsToSetFactory.make(cto));
                    }
                }
            });
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }
        public Void visit(Copy stmt) {
            Var x = stmt.getLValue();
            Var y = stmt.getRValue();
            CSVar cx = csManager.getCSVar(context,x);
            CSVar cy = csManager.getCSVar(context,y);
            addPFGEdge(cy,cx);
            return StmtVisitor.super.visit(stmt);
        }
        public Void visit(New stmt) {
            Obj o = heapModel.getObj(stmt);
            Context c = contextSelector.selectHeapContext(csMethod,o);
            CSObj co = csManager.getCSObj(c,o);
            PointsToSet pts = PointsToSetFactory.make(co);
            Var x = stmt.getLValue();
            CSVar cx = csManager.getCSVar(context,x); //这里和ppt上不一样，两个上下文有区别的
            workList.addEntry(cx,pts);
            return StmtVisitor.super.visit(stmt);
        }
        public Void visit(LoadField stmt) {//y = T.f
            if(stmt.isStatic()){
                Var y =stmt.getLValue();
                CSVar cy = csManager.getCSVar(context,y);
                StaticField sf = csManager.getStaticField(stmt.getFieldRef().resolve());
                addPFGEdge(sf, cy);
            }
            return StmtVisitor.super.visit(stmt);
        }
        public Void visit(StoreField stmt) {//T.f = y
            if(stmt.isStatic()){
                Var y = stmt.getRValue();
                CSVar cy = csManager.getCSVar(context,y);
                StaticField sf = csManager.getStaticField(stmt.getFieldRef().resolve());
                addPFGEdge(cy,sf);
            }
            return StmtVisitor.super.visit(stmt);
        }
        public Void visit(Invoke stmt) {
            if(stmt.isStatic()){
                JMethod m = stmt.getMethodRef().resolve();

                CSCallSite csc = csManager.getCSCallSite(context,stmt);
                Context ct = contextSelector.selectContext(csc,m);
                CSMethod cm = csManager.getCSMethod(ct,m);
                if(callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(stmt),csc,cm))){
                    //.addReachableMethod(m);
                    addReachable(cm);
                    int size = m.getIR().getParams().size();
                    for(int i=0;i<size;i++){
                        addPFGEdge(csManager.getCSVar(context,stmt.getInvokeExp().getArg(i)),
                                csManager.getCSVar(ct,m.getIR().getParam(i)));
                    }
                    for(Var v :m.getIR().getReturnVars()){
                        Var l = stmt.getLValue();
                        if(l!=null){
                            addPFGEdge(csManager.getCSVar(ct,v),csManager.getCSVar(context,l));
                        }

                    }
                }
            }
            return StmtVisitor.super.visit(stmt);
        }

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if(pointerFlowGraph.addEdge(source,target)){
            PointsToSet ptss = source.getPointsToSet();
            if(!ptss.isEmpty()){
                workList.addEntry(target,ptss);
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        while(!workList.isEmpty()){
            WorkList.Entry et =workList.pollEntry();
            Pointer n = et.pointer();
            PointsToSet pts = et.pointsToSet();
            PointsToSet delta = propagate(n,pts);
            if(n instanceof CSVar){
                Var x = ((CSVar) n).getVar();
                Context c = ((CSVar) n).getContext();
                for (CSObj o:
                        delta) {
                    for(StoreField sf:x.getStoreFields()){//x.f = y
                        addPFGEdge(csManager.getCSVar(c,sf.getRValue()),
                                csManager.getInstanceField(o,sf.getFieldRef().resolve()));
                    }
                    for(LoadField lf:x.getLoadFields()){// y = x.f
                        addPFGEdge(csManager.getInstanceField(o, lf.getFieldRef().resolve()),
                                csManager.getCSVar(c,lf.getLValue()));
                    }
                    for(LoadArray la:x.getLoadArrays()){//y = x[i]
                        addPFGEdge(csManager.getArrayIndex(o),
                                csManager.getCSVar(c,la.getLValue()));
                    }
                    for(StoreArray sa:x.getStoreArrays()){ //x[i] = y
                        addPFGEdge(csManager.getCSVar(c,sa.getRValue()),
                                csManager.getArrayIndex(o));
                    }
                    CSVar cx = csManager.getCSVar(c,x);
                    processCall(cx,o);
                    Map<Pointer,PointsToSet> taintmap = taintAnalysis.taintpropagate(cx,o,x.getMethod());
                    taintmap.forEach((pointer,pointstoset)->{
                        workList.addEntry(pointer,pointstoset);
                    });
                }
            }
        }
        // TODO - finish me
    }
    private  PointsToSet minus(PointsToSet a,PointsToSet b){ // a - b
        PointsToSet res = PointsToSetFactory.make();
        for(CSObj o:a){
            if(!b.contains(o)){
                res.addObject(o);
            }
        }
        return res;
    }
    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        PointsToSet ptsn = pointer.getPointsToSet();
        PointsToSet delta = minus(pointsToSet,ptsn);
        if(!delta.isEmpty()){
            for(CSObj o:delta){
                pointer.getPointsToSet().addObject(o);
            }
            Set<Pointer> set = pointerFlowGraph.getSuccsOf(pointer);
            for (Pointer s:set){
                workList.addEntry(s,delta);
            }
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        for(Invoke invoke : recv.getVar().getInvokes()){
            JMethod m = resolveCallee(recvObj,invoke);
            Var mthis = m.getIR().getThis();
            Context c = recv.getContext();
            CSCallSite cs = csManager.getCSCallSite(c,invoke);//c:l
            Context ct = contextSelector.selectContext(cs,recvObj,m);
            CSMethod ctm = csManager.getCSMethod(ct,m);
            workList.addEntry(csManager.getCSVar(ct,mthis),PointsToSetFactory.make(recvObj));
            if(callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke),cs,ctm))){
                addReachable(ctm);
                int size = m.getIR().getParams().size();
                for(int i=0;i<size;i++){
                    addPFGEdge(csManager.getCSVar(c,invoke.getInvokeExp().getArg(i)),
                            csManager.getCSVar(ct,m.getIR().getParam(i)));
                }
                for(Var v :m.getIR().getReturnVars()){
                    Var l = invoke.getLValue();
                    if(l!=null){
                        addPFGEdge(csManager.getCSVar(ct,v), csManager.getCSVar(c,l));
                    }

                }

            }
        }
        // TODO - finish me
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    public JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    public PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
