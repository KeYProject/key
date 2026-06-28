package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public sealed interface Declaration {

    @Nullable()
    @java.lang.Override()
    abstract Position position();

    @java.lang.Override()
    abstract Declaration setPosition(@Nullable() Position value);
}
