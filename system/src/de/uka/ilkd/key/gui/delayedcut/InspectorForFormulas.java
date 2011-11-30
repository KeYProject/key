package de.uka.ilkd.key.gui.delayedcut;

import java.io.StringReader;

import de.uka.ilkd.key.gui.delayedcut.CheckedUserInput.CheckedUserInputInspector;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.KeYLexer;
import de.uka.ilkd.key.parser.KeYParser;
import de.uka.ilkd.key.parser.ParserMode;
import de.uka.ilkd.key.proof.Node;

public class InspectorForFormulas implements CheckedUserInputInspector{

    private final Services services;
    private final Node node;
    
    
    
    public InspectorForFormulas(Services services, Node node) {
        super();
        this.services = services;
        this.node = node;
    }



    @Override
    public String check(String toBeChecked) {
        Term term = translate(services,toBeChecked);
        for(SequentFormula sf : node.sequent()){
            if(sf.formula() == term){
                return "Formula already exists in sequent.";
            }
        }
       if(term == null){
           return "Syntax error.";
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
