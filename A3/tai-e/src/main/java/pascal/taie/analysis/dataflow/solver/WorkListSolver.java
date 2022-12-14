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

package pascal.taie.analysis.dataflow.solver;

import fj.data.List;
import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;

import java.util.ArrayList;
import java.util.Set;
class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me
        ArrayList<Node> l = new ArrayList<>();
        for (Node node : cfg){
            l.add(node);
        }
        while (!l.isEmpty()){
            Node b = l.get(0);
            l.remove(0);
            for (Node pred : cfg.getPredsOf(b)) {
                analysis.meetInto(result.getOutFact(pred),result.getInFact(b));
                if(analysis.transferNode(b,result.getInFact(b),result.getOutFact(b))){
                    for(Node succ:cfg.getSuccsOf(b)){
                        l.add(succ);
                    }
                }
            }
        }

    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        boolean flag;
        do{
            flag = false;
            for (Node node : cfg) {
                if(cfg.isExit(node))continue;
                for (Node succ : cfg.getSuccsOf(node)) {
                    analysis.meetInto(result.getInFact(succ),result.getOutFact(node));
                }
                if(analysis.transferNode(node, result.getInFact(node), result.getOutFact(node) )){
                    flag = true;//changes happen to in
                }
            }
        }while (flag);
        // TODO - finish me
    }


}
