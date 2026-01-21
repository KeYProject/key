package de.uka.ilkd.key.logic;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.op.IProgramMethod;

public class MethodStackInfo implements NameCreationInfo {

    public static NameCreationInfo create(ProgramElement program) {
        return new MethodStackInfo(program);
    }

    private final ProgramElement element;


    public MethodStackInfo(ProgramElement element) {
        this.element = element;
    }

    /**
     * returns the method call stack
     */
    public ImmutableList<IProgramMethod> getMethodStack() {
        ImmutableList<IProgramMethod> list = ImmutableSLList.<IProgramMethod>nil();
        if (element instanceof ProgramPrefix) {
            final ImmutableArray<ProgramPrefix> prefix =
                ((ProgramPrefix) element).getPrefixElements();
            for (int i = prefix.size() - 1; i >= 0; i--) {
                if (prefix.get(i) instanceof MethodFrame) {
                    final MethodFrame frame = (MethodFrame) prefix.get(i);
                    IProgramMethod method = frame.getProgramMethod();
                    if (method != null) {
                        list = list.prepend(method);
                    }
                }
            }
        }
        return list;
    }


    public String infoAsString() {
        String result = "Method stack:\n";

        for (IProgramMethod method : getMethodStack()) {
            result += "- " + method.getProgramElementName().toString() + "\n";
        }

        if (result.length() < 1)
            return "";

        result = result.substring(0, result.length() - 1);

        return result;
    }



}
