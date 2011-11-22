package de.uka.ilkd.key.gui.delayedcut;

import java.io.StringReader;

import de.uka.ilkd.key.gui.delayedcut.CheckedUserInput.CheckedUserInputInspector;
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
    public boolean check(String toBeChecked) {
        Term term = translate(services,toBeChecked);
       return term != null && term.sort() == Sort.FORMULA;

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
