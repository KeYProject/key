package de.uka.ilkd.key.logic.label;

import java.util.List;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.TermLabel;

public interface TermLabelFactory<T extends TermLabel> extends Named {

    @Override
    public Name name();

    public T parse(List<String> arguments) throws TermLabelException;

    public T create(List<?> parameters) throws TermLabelException;

}
