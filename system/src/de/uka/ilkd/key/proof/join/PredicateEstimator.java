// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.proof.join;

import java.io.StringReader;
import java.util.Comparator;
import java.util.Iterator;
import java.util.TreeSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.parser.KeYLexer;
import de.uka.ilkd.key.parser.KeYParser;
import de.uka.ilkd.key.parser.ParserMode;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

public interface PredicateEstimator {
    public static final PredicateEstimator STD_ESTIMATOR = new StdPredicateEstimator();
    
    /**
     * returns a decision predicate for the two nodes in partner. The predicate should be true 
     * in the sequent of the first node and false in the sequent of the second node.
     */
    public Result estimate(ProspectivePartner partner, Proof proof);
    
    public interface Result{
        Term getPredicate();
        Node getCommonParent();
    }
}


class StdPredicateEstimator implements PredicateEstimator{
    
    @Override
    public Result estimate(ProspectivePartner partner, Proof proof){
           final Node node = getFirstDifferentNode(partner);
           String branchLabel = node.getNodeInfo().getBranchLabel();
           if(branchLabel != null && (branchLabel.endsWith("TRUE") || branchLabel.endsWith("FALSE") )){
               final boolean positive = branchLabel.endsWith("TRUE");
               String suffix = positive ? "TRUE" : "FALSE";
               int index = branchLabel.lastIndexOf(suffix);
               branchLabel = branchLabel.substring(0, index);      
               
               String cut = "CUT:";
               if(branchLabel.startsWith(cut)){
                   branchLabel = branchLabel.substring(cut.length());
               }
               
          
               final Term term = translate(branchLabel,proof.getServices());
               
               if(term != null){
                   return new Result() {
                    
                    @Override
                    public Term getPredicate() {
                        if(!positive){
                            return TermBuilder.DF.not(term);
                        }
                        return term;
                    }
                    
                    @Override
                    public Node getCommonParent() {
                        return node.parent();
                    }
                };
                   
               }
               
         
           }
        
        return new Result(){

            @Override
            public Term getPredicate() {
                return null;
            }

            @Override
            public Node getCommonParent() {
                return node.parent();
            }
            
        };
    }
    
    /**
     * goes up to the common node of partner.getNode(0) and partner.getNode(1) and returns
     * the next node on the path to partner.getNode(0).
     */
    private Node getFirstDifferentNode(ProspectivePartner partner){
            TreeSet<Node> set = new TreeSet<Node>(new Comparator<Node>() {

                @Override
                public int compare(Node o1, Node o2) {
                    
                    return o1.serialNr()-o2.serialNr();
                }
            });
        

            Node node = partner.getNode(0);
            while(!node.root()){
                set.add(node);
                node = node.parent();
            }
            if(node.root()){
                set.add(node);                 
            }
            
            node = partner.getNode(1);
            while(node.parent() != null && !set.contains(node)){
                node = node.parent();
            }
            
                      
            if(set.contains(node)){
                Iterator<Node> it = node.childrenIterator();
                while(it.hasNext()){
                    Node child = it.next();
                    if(set.contains(child)){
                        return child;
                    }
                }
            }                
              
        
        return null;
    }
    
    private Term translate(String estimation, Services services){
            try {
            KeYParser parser =
                    new KeYParser (ParserMode.TERM, new KeYLexer ( new StringReader ( estimation ),
                                     services.getExceptionHandler() ), "",
                                     services,   // should not be needed
                                     services.getNamespaces() );
                return parser.term();
             } catch (Throwable e) {
                 
                return null;
             }
    }
    

    
    
}