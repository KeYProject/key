package de.uka.ilkd.key.logic.label;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.label.OriginTermLabel.Origin;
import de.uka.ilkd.key.logic.label.OriginTermLabel.SpecType;

public class OriginTermLabelFactory implements TermLabelFactory<OriginTermLabel> {

    @Override
    public OriginTermLabel parseInstance(List<String> arguments, TermServices services) throws TermLabelException {
        if (arguments.size() != OriginTermLabel.CHILD_COUNT) {
            throw new TermLabelException(
                    "OriginTermLabel has "
                            + arguments.size()
                            + " children, but should have " + OriginTermLabel.CHILD_COUNT);
        }
        
        Origin origin = parseOrigin(arguments.get(0));
        Set<Origin> subtermOrigins = parseSubtermOrigins(arguments.get(1));
        
        return new OriginTermLabel(origin, subtermOrigins);
    }
    
    private Set<Origin> parseSubtermOrigins(String str) throws TermLabelException {
        if (!str.startsWith("[") || !str.endsWith("]")) {
            throw new TermLabelException("Malformed set of origins: \"" + str + "\"\n"
                    + "(Should be a comma-separated set of of origins, delimited by \"[\" and \"]\"");
        }
        
        Set<Origin> result = new HashSet<>();
        
        for (String s : str.substring(1, str.length() - 1).split("\\s*,\\s*")) {
            result.add(parseOrigin(s));
        }
        
        return result;
    }

    private Origin parseOrigin(String str) throws TermLabelException {
        try {
            String[] arr = str.split("\\s*((@ line)|@)\\s*");
            
            SpecType specType = parseSpecType(arr[0]);
            String filename = arr[1];
            int line = Integer.parseInt(arr[2]);
            
            return new Origin(specType, filename, line);
        } catch (ArrayIndexOutOfBoundsException | IllegalArgumentException e) {
            throw new TermLabelException("Malformed origin string: \"" + str + "\"\n"
                    + "(Well-formed origins look like this: \"spec_type @ filename @ line xx\")");
        } 
    }

    private SpecType parseSpecType(String str) {
        if (str.toLowerCase().equals(SpecType.NONE.toString())) {
            str = "none";
        }
        
        return SpecType.valueOf(str.toUpperCase());
    }
}
