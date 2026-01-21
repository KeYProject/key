package recoder.list.generic;

import recoder.java.SourceElement;

import java.util.List;

public interface ASTList<E extends SourceElement> extends List<E> {
    ASTList<E> deepClone();

    void trimToSize();
}
