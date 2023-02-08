package de.uka.ilkd.key.java.statement;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.java.LoopInitializer;
import de.uka.ilkd.key.java.TerminalProgramElement;

public interface ILoopInit extends TerminalProgramElement {

    int size();

    ImmutableArray<LoopInitializer> getInits();

}
