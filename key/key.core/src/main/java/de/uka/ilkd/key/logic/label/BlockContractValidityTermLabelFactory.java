package de.uka.ilkd.key.logic.label;

import java.util.List;

import org.key_project.util.java.ObjectUtil;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.ProgramVariable;

/**
 * A factory for creating {@link BlockContractValidityTermLabel} objects.
 */
public class BlockContractValidityTermLabelFactory
        implements TermLabelFactory<BlockContractValidityTermLabel> {
    /**
     * {@inheritDoc}
     *
     * <p>
     * This method accepts single arguments which can be parsed as a {@link String}.
     */
    @Override
    public BlockContractValidityTermLabel parseInstance(List<String> parameters,
            TermServices services) throws TermLabelException {
        if (parameters == null || parameters.size() != 1) {
            throw new TermLabelException("Label " + BlockContractValidityTermLabel.NAME
                + " requires exactly one String-Parameter with the name of the exception variable.");
        }
        String val = ObjectUtil.toString(parameters.get(0));
        if (StringUtil.isTrimmedEmpty(val)) {
            throw new TermLabelException("Label " + BlockContractValidityTermLabel.NAME
                + " requires exactly one String-Parameter with the name of the exception variable.");
        }
        return new BlockContractValidityTermLabel(
            (ProgramVariable) services.getNamespaces().programVariables().lookup(val));
    }
}
