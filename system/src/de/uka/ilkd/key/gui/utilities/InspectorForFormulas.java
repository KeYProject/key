package de.uka.ilkd.key.gui.utilities;

import java.io.StringReader;

import de.uka.ilkd.key.gui.utilities.CheckedUserInput.CheckedUserInputInspector;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.KeYLexer;
import de.uka.ilkd.key.parser.KeYParser;
import de.uka.ilkd.key.parser.ParserMode;


public class InspectorForFormulas implements CheckedUserInputInspector{

    private final Services services;

    
    
    
    public InspectorForFormulas(Services services) {
        super();
        this.services = services;
    }



    @Override
    public String check(String toBeChecked) {
        if(toBeChecked.isEmpty()){
            return CheckedUserInputInspector.NO_USER_INPUT;
        }
        Term term = translate(services,toBeChecked);
         
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