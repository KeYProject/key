package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;

public interface AbstractProgramElement extends ProgramElement {

    ProgramElement getConcreteProgramElement(Services services);

}
