package de.uka.ilkd.key.logic.label;

import java.util.List;

import de.uka.ilkd.key.logic.TermServices;

public class OriginTermLabelFactory implements TermLabelFactory<OriginTermLabel> {

    @Override
    public OriginTermLabel parseInstance(List<String> arguments, TermServices services) throws TermLabelException {
        // TODO Auto-generated method stub
        System.out.println("parsing OriginTermLabel");
        
        for (String arg : arguments) {
            System.out.println("\t" + arg);
        }
        
        return null;
    }

}
