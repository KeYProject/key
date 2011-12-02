package de.uka.ilkd.key.gui;

import java.io.StringReader;

import de.uka.ilkd.key.gui.utilities.CheckedUserInput.CheckedUserInputInspector;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.KeYLexer;
import de.uka.ilkd.key.parser.KeYParser;
import de.uka.ilkd.key.parser.ParserMode;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.delayedcut.DelayedCut;

public class InspectorForDecisionPredicates implements CheckedUserInputInspector{

    private final Services services;
    private final Node node;
    private final int  cutMode;
    
    
    
    public InspectorForDecisionPredicates(Services services, Node node, int cutMode) {
        super();
        this.services = services;
        this.node = node;
        this.cutMode = cutMode;
    }



    @Override
    public String check(String toBeChecked) {
        if(toBeChecked.isEmpty()){
            return CheckedUserInputInspector.NO_USER_INPUT;
        }
        Term term = translate(services,toBeChecked);
        Semisequent semisequent = cutMode == DelayedCut.DECISION_PREDICATE_IN_ANTECEDENT ? 
                node.sequent().antecedent() : node.sequent().succedent();
        String position = cutMode == DelayedCut.DECISION_PREDICATE_IN_ANTECEDENT ? "antecedent":"succedent";   
        
        for(SequentFormula sf : semisequent){
            if(sf.formula() == term){
                return "Formula already exists in "+position+".";
            }
        }
        
       if(term == null){
           return NO_USER_INPUT;
       }
       
       if(term.sort() != Sort.FORMULA){
           return "Not a formula.";
       }
       return null;

    }
    
    public static Term translate(Services services, String toBeChecked){
        try {
            KeYParser parser =
                    new KeYParser (ParserMode.TERM, new KeYLexer ( new StringReader ( toBeChecked ),
                                     services.getExceptionHandler() ), "",
                                     services,   // should not be needed
                                     services.getNamespaces() );
                return parser.term();
             } catch (Throwable e) {
                 
                return null;
             }
    }

}
