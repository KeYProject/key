package org.key_project.java.ast;

import org.jspecify.annotations.Nullable;
import de.uka.ilkd.key.speclang.jml.pretranslation.*;
import de.uka.ilkd.key.java.ast.PositionInfo;
import org.key_project.util.collection.*;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import org.key_project.logic.op.sv.*;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.abstraction.Type;
import java.util.*;
import org.jspecify.annotations.NullMarked;

@NullMarked()
public sealed interface MethodDeclaration extends JavaDeclaration, MemberDeclaration, ParameterContainer, NamedProgramElement, TypeReferenceContainer, Matchable, Visitable permits ConstructorDeclaration {

    TypeReference returnType();

    ImmutableList<Comment> voidComments();

    ProgramElementName name();

    ImmutableList<ParameterDeclaration> parameters();

    Throws exceptions();

    StatementBlock body();

    JMLModifiers jmlModifiers();

    boolean parentIsInterfaceDeclaration();
}
