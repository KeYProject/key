package de.uka.ilkd.key.java.visitor;

import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.util.ExtList;

public class ProgramElementReplacer extends CreatingASTVisitor {

    private ProgramElement oldElement;
    private ProgramElement newElement;
    private boolean done;

    public ProgramElementReplacer(JavaProgramElement program, Services services)
    {
        super(program, false, services);
    }

    public ProgramElement replace(ProgramElement oldElement, ProgramElement newElement)
    {
        this.oldElement = oldElement;
        this.newElement = newElement;
        done = false;
        stack.push(new ExtList());
        walk(root());
        ExtList el = stack.peek();
        return el.get(ProgramElement.class);
    }

    protected void doAction(ProgramElement element)
    {
        if (!done && element == oldElement) {
            done = true;
            addChild(newElement);
            changed();
        }
        else {
            super.doAction(element);
        }
    }

}