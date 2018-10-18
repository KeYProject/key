package de.uka.ilkd.key.java.visitor;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;

public class LoopInitASTVisitor extends CreatingASTVisitor {
	private ProgramElement result = null;
	
	public LoopInitASTVisitor(ProgramElement root, boolean preservesPos, Services services) {
		super(root, preservesPos, services);
	}

	
}
