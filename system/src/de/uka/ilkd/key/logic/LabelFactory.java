package de.uka.ilkd.key.logic;

/**
 * Factory class for term labels
 * 
 * Attention: TermLabels used as patterns or construction labels are provided by the
 * label factory in package rule.label
 */
public class LabelFactory {

    public static ITermLabel createLabel(String name) throws UnknownLabelException {
        switch (name) {
            case "SE" : return SymbolicExecutionLabel.INSTANCE;            
        }
        throw new UnknownLabelException(name);
    }

}
