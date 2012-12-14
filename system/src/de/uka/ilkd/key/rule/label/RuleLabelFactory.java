package de.uka.ilkd.key.rule.label;

import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.logic.LabelFactory;
import de.uka.ilkd.key.logic.UnknownLabelException;


public class RuleLabelFactory extends LabelFactory {

    public static ITermLabel createLabel(String name) throws UnknownLabelException {
        switch (name) {
            case "*" : return TermLabelWildcard.WILDCARD;            
            default:
                return LabelFactory.createLabel(name);
        }
    }    
    
}
