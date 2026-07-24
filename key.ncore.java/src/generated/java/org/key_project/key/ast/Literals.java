package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public sealed interface Literals permits BooleanLiteral, CharLiteral, FloatLiteral, IntegerLiteral, StringLiteral {
}
