package recoder.list.generic;

import java.util.ArrayList;
import java.util.Collection;

import recoder.java.SourceElement;

public class ASTArrayList<E extends SourceElement> extends ArrayList<E> implements ASTList<E> {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 3179494289054893052L;

    public ASTArrayList() {
        super();
    }

    public ASTArrayList(Collection<E> c) {
        super(c);
    }

    public ASTArrayList(int initialCapacity) {
        super(initialCapacity);
    }

    public ASTArrayList(E initialItem) {
        this(1);
        add(initialItem);
    }

    public ASTArrayList<E> deepClone() {
        ASTArrayList<E> result = new ASTArrayList<>(size());
        for (E e : this) {
            @SuppressWarnings("unchecked")
            E deepClone = (E) e.deepClone();
            result.add(deepClone);
        }
        return result;
    }

}
