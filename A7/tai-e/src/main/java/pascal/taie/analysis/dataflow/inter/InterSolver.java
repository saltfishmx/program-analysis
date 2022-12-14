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

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.analysis.graph.icfg.ICFGEdge;
import pascal.taie.util.collection.SetQueue;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Solver for inter-procedural data-flow analysis.
 * The workload of inter-procedural analysis is heavy, thus we always
 * adopt work-list algorithm for efficiency.
 */
class InterSolver<Method, Node, Fact> {

    private final InterDataflowAnalysis<Node, Fact> analysis;

    private final ICFG<Method, Node> icfg;

    private DataflowResult<Node, Fact> result;

    private Queue<Node> workList;

    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
                ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        this.icfg = icfg;
    }

    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        initialize();
        doSolve();
        return result;
    }

    private void initialize() {
        // TODO - finish me
        Stream<Method> st = icfg.entryMethods();
        Set<Node> s = new HashSet<>();
        st.forEach(m->{
            Node n = icfg.getEntryOf(m);
            s.add(n);
            result.setOutFact(n, analysis.newBoundaryFact(n));
        });
        for(Node n:icfg){
            if(!s.contains(n)){
                result.setOutFact(n, analysis.newInitialFact());
            }
        }
    }

    private void doSolve() {
        ArrayList<Node> l = new ArrayList<>();
        for (Node node : icfg){
            l.add(node);
        }
        for (Node node : icfg){
            l.add(node);
        }
        while(!l.isEmpty()){
            Node b = l.get(0);
            l.remove(0);
            Set<ICFGEdge<Node>> s= icfg.getInEdgesOf(b);
            Set<ICFGEdge<Node>> s1= new HashSet<>();
            Set<ICFGEdge<Node>> s2= new HashSet<>();
            for (ICFGEdge<Node> n:
                 s) {
                if(n instanceof CallToReturnEdge<Node>){
                    s1.add(n);
                }
                else{
                    s2.add(n);
                }
            }
            Fact inb = analysis.newInitialFact();
            for (ICFGEdge<Node> e : s1) {
                Node pred = e.getSource();
                analysis.meetInto(analysis.transferEdge(e, result.getOutFact(pred)), inb);
            }
            for (ICFGEdge<Node> e : s2) {
                Node pred = e.getSource();
                analysis.meetInto(analysis.transferEdge(e, result.getOutFact(pred)), inb);
            }
            result.setInFact(b,inb);
            if(analysis.transferNode(b,result.getInFact(b),result.getOutFact(b))){
                for(Node succ:icfg.getSuccsOf(b)){
                    l.add(succ);
                }
            }
        }

        // TODO - finish me
    }
    public List<Node> getStmtList()
    {
        List<Node> list=new LinkedList<>();
        for(Node node:icfg)
            list.add(node);
        return list;
    }
    public DataflowResult<Node, Fact> getResult(){
        return result;
    }
}
