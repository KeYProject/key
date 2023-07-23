package de.uka.ilkd.key.logic.overop;

import de.uka.ilkd.key.logic.op.Function;

import javax.annotation.Nullable;

public interface FunctionMetaData {
    int getPrecedence();

    default boolean isInfix() {
        return false;
    }

    default boolean isPrefix(){
        return false;
    }

    default boolean isSuffix(){
        return false;
    }

    default boolean isShortcut(){
        return false;
    }

    String getUnicode();
    @Nullable String getLongForm();

    Iterable<String> getAlternativeSignatures(Function fun);
}
