/**
 * This package contains the metamodel abstractions as used by the
 * semantical services. The {@link recoder.abstraction.ProgramModelElement}s
 * hide the origin of the information, be it from Java source code,
 * Java byte code, or predefined lacking any syntactical representation.
 * <p>
 * There are three implicitly defined entities -
 * {@link recoder.abstraction.ArrayType},
 * {@link recoder.abstraction.DefaultConstructor}, and
 * {@link recoder.abstraction.Package}, as well as the predefined
 * types {@link recoder.abstraction.NullType} and the base class for
 * the small number of {@link recoder.abstraction.PrimitiveType}s.
 * <p>
 * scopes are attached to {@link recoder.java.ScopeDefiningElement}s by
 * {@link recoder.service.SourceInfo} implementations and should
 * not be modified from others.
 */
package de.uka.ilkd.key.java.abstraction;
