package de.uka.ilkd.key.java.ast.statement;

import de.uka.ilkd.key.java.ast.LoopInitializer;
import de.uka.ilkd.key.java.ast.TerminalProgramElement;

import org.key_project.util.collection.ImmutableArray;

public interface ILoopInit extends TerminalProgramElement {

    int size();

    ImmutableArray<LoopInitializer> getInits();

}
