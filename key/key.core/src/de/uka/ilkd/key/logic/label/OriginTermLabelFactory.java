package de.uka.ilkd.key.logic.label;

import java.util.List;

import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.label.OriginTermLabel.SpecType;
import de.uka.ilkd.key.parser.schemajava.ParseException;

public class OriginTermLabelFactory implements TermLabelFactory<OriginTermLabel> {

    @Override
    public OriginTermLabel parseInstance(List<String> arguments, TermServices services) throws TermLabelException {
        if (arguments.size() != OriginTermLabel.CHILD_COUNT) {
            throw new ParseException(
                    "OriginTermLabel has "
                            + arguments.size()
                            + " children, but should have " + OriginTermLabel.CHILD_COUNT);
        }
        
        String originStr = arguments.get(0);
        String[] originStrSep = originStr.split("\\s*(@|(, line))\\s*");
        
        SpecType specType = SpecType.valueOf(originStrSep[0]);
        String filename = originStrSep[1];
        int line = Integer.parseInt(originStrSep[2]);
        
        
        String subtermOriginsStr = arguments.get(1);
        
        
        
        return null;
    }

}
