package de.uka.ilkd.key.rule.label;

import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.logic.LabelFactory;
import de.uka.ilkd.key.logic.UnknownLabelException;


public class RuleLabelFactory extends LabelFactory {

    public static ITermLabel createLabel(String name) throws UnknownLabelException {
        if ("*".equals(name)) {
            return TermLabelWildcard.WILDCARD;
        }
        else {
            return LabelFactory.createLabel(name);
        }
    }    

    
    public static ITermLabel createLabelUnion(ITermLabel left, ITermLabel right) throws UnknownLabelException {
        return new TermLabelUnion(left, right);
    }    
    
    public static ITermLabel createLabelIntersection(ITermLabel left, ITermLabel right) throws UnknownLabelException {
       return new TermLabelIntersection(left, right);
   }    

    public static ITermLabel createLabelSubstraction(ITermLabel left, ITermLabel right) throws UnknownLabelException {
        return new TermLabelSubstraction(left, right);
    }    

}
