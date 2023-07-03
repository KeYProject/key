package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.ProgramElement;

public interface AbstractProgramElement extends ProgramElement {

    ProgramElement getConcreteProgramElement(Services services);

}
