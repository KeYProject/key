// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java;

import org.key_project.util.ExtList;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.io.IOException;
import java.io.StringWriter;
import java.net.URI;
import java.util.Objects;


/**
 * Top level implementation of a Java {@link SourceElement}.
 * <p>
 * This class is intended to be immutable.
 */
public abstract class JavaSourceElement implements SourceElement {
    private static final Logger LOGGER = LoggerFactory.getLogger(JavaSourceElement.class);

    @Nonnull
    private final PositionInfo posInfo;


    public JavaSourceElement() {
        posInfo = PositionInfo.UNDEFINED;
    }


    /**
     * @param pi PositionInfo the PositionInfo of the element
     */
    public JavaSourceElement(@Nullable PositionInfo pi) {
        posInfo = getPosInfo(pi);
    }

    /**
     * @param children a list of the children of this element. May contain:
     *                 PositionInfo
     */
    @Deprecated
    public JavaSourceElement(ExtList children) {
        posInfo = getPosInfo(children.get(PositionInfo.class));

    }

    @Deprecated
    public JavaSourceElement(ExtList children, PositionInfo pos) {
        posInfo = getPosInfo(pos);
    }

    /**
     * Internal method use to guarantee the position info object is
     * always not the null reference
     *
     * @param p a PositionInfo
     * @return if {@code p} is {@code null} the undefined
     * position ({@link PositionInfo#UNDEFINED}) is returned otherwise
     * {@code p}
     */
    @Nonnull
    private static PositionInfo getPosInfo(PositionInfo p) {
        return Objects.requireNonNullElse(p, PositionInfo.UNDEFINED);
    }


    /**
     * Finds the source element that occurs first in the source. The default
     * implementation returns this element, which is correct for all terminal
     * program elements, and many non terminals such as statements and prefixed
     * operators.
     *
     * @return the first source element in the syntactical representation of
     * this element, may be equals to this element.
     * @see #toSource()
     * @see #getStartPosition()
     */
    @Nonnull
    public SourceElement getFirstElement() {
        return this;
    }

    @Override
    public SourceElement getFirstElementIncludingBlocks() {
        return getFirstElement();
    }

    /**
     * Finds the source element that occurs last in the source.  The
     * default implementation returns this element, which is correct
     * for all terminal program elements, and many non terminals such
     * as statements and prefixed operators.
     *
     * @return the last source element in the syntactical representation of
     * this element, may be equals to this element.
     * @see #toSource()
     * @see #getEndPosition()
     */
    @Nonnull
    public SourceElement getLastElement() {
        return this;
    }


    /**
     * Creates a syntactical representation of the source element using
     * the {@link #prettyPrint} method.
     */
    public String toSource() {
        return toString();
    }

    /**
     * Returns the start position of the primary token of this element.
     * To get the start position of the syntactical first token,
     * call the corresponding method of <CODE>getFirstElement()</CODE>.
     *
     * @return the start position of the primary token.
     */
    @Nonnull
    public Position getStartPosition() {
        return posInfo.getStartPosition();
    }

    /**
     * Returns the end position of the primary token of this element.
     * To get the end position of the syntactical first token,
     * call the corresponding method of <CODE>getLastElement()</CODE>.
     *
     * @return the end position of the primary token.
     */
    public Position getEndPosition() {
        return posInfo.getEndPosition();
    }

    /**
     * Returns the relative position (number of blank heading lines and
     * columns) of the primary token of this element.
     * To get the relative position of the syntactical first token,
     * call the corresponding method of <CODE>getFirstElement()</CODE>.
     *
     * @return the relative position of the primary token.
     */
    public Position getRelativePosition() {
        return posInfo.getRelativePosition();
    }


    public PositionInfo getPositionInfo() {
        return posInfo;
    }


    /**
     * toString
     */
    public String toString() {
        StringWriter sw = new StringWriter();
        PrettyPrinter pp = new PrettyPrinter(sw, true);
        return toString(pp, sw);
    }

    /*Sometimes CompilableJavaPP must be given as argument instead of the ordinary PrettyPrinter */
    public String toString(PrettyPrinter pp, StringWriter sw) {
        try {
            pp.setIndentationLevel(0);
            prettyPrint(pp);
        } catch (IOException e) {
            LOGGER.error("Pretty printing of JavaSourceElement failed", e);
        }
        String r = sw.toString();
        r = r.replace('\n', ' ');
        r = r.replace('\t', ' ');
        return r;
    }


    /**
     * this violates immutability, but the method is only called
     * right after the object is created...
     *
     * @param s the path of the parent class as String
     */
    protected void setParentClass(URI s) {
        posInfo.setParentClassURI(s);
    }

    /**
     * get the class the statement originates from
     */
    public String getParentClass() {
        return posInfo.getParentClass();
    }

}