/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java;

import java.net.URI;

import de.uka.ilkd.key.pp.PrettyPrinter;

import org.key_project.util.ExtList;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;


/**
 * Top level implementation of a Java {@link SourceElement}. taken from COMPOST and changed to
 * achieve an immutable structure
 */
public abstract class JavaSourceElement implements SourceElement {
    private static final Logger LOGGER = LoggerFactory.getLogger(JavaSourceElement.class);

    private final PositionInfo posInfo;


    /**
     * Java source element.
     */
    public JavaSourceElement() {
        posInfo = PositionInfo.UNDEFINED;
    }


    /**
     * Java source element.
     *
     * @param pi PositionInfo the PositionInfo of the element
     */
    public JavaSourceElement(PositionInfo pi) {
        posInfo = getPosInfo(pi);
    }

    /**
     * Java source element.
     *
     * @param children a list of the children of this element. May contain: PositionInfo
     */
    public JavaSourceElement(ExtList children) {
        posInfo = getPosInfo(children.get(PositionInfo.class));

    }

    public JavaSourceElement(ExtList children, PositionInfo pos) {
        posInfo = getPosInfo(pos);
    }

    /**
     * internal method use to guarantee the position info object is always not the null reference
     *
     * @param p a PositionInfo
     * @return if <tt>p</tt> is <tt>null</tt> the undefined position
     *         ({@link PositionInfo#UNDEFINED}) is returned otherwise <tt>p</tt>
     */
    private PositionInfo getPosInfo(PositionInfo p) {
        final PositionInfo pos;
        if (p == null) {
            pos = PositionInfo.UNDEFINED;
        } else {
            pos = p;
        }
        return pos;
    }



    /**
     * Finds the source element that occurs first in the source. The default implementation returns
     * this element, which is correct for all terminal program elements, and many non terminals such
     * as statements and prefixed operators.
     *
     * @return the first source element in the syntactical representation of this element, may be
     *         equals to this element.
     * @see #toSource()
     * @see #getStartPosition()
     */

    public SourceElement getFirstElement() {
        return this;
    }

    @Override
    public SourceElement getFirstElementIncludingBlocks() {
        return getFirstElement();
    }

    /**
     * Finds the source element that occurs last in the source. The default implementation returns
     * this element, which is correct for all terminal program elements, and many non terminals such
     * as statements and prefixed operators.
     *
     * @return the last source element in the syntactical representation of this element, may be
     *         equals to this element.
     * @see #toSource()
     * @see #getEndPosition()
     */

    public SourceElement getLastElement() {
        return this;
    }

    /**
     * Creates a syntactical representation of the source element using the pretty printer.
     */
    public String toSource() {
        return toString();
    }

    /**
     * Returns the start position of the primary token of this element. To get the start position of
     * the syntactical first token, call the corresponding method of <CODE>getFirstElement()</CODE>.
     *
     * @return the start position of the primary token.
     */
    public Position getStartPosition() {
        return posInfo.getStartPosition();
    }

    /**
     * Returns the end position of the primary token of this element. To get the end position of the
     * syntactical first token, call the corresponding method of <CODE>getLastElement()</CODE>.
     *
     * @return the end position of the primary token.
     */
    public Position getEndPosition() {
        return posInfo.getEndPosition();
    }

    /**
     * Returns the relative position (number of blank heading lines and columns) of the primary
     * token of this element. To get the relative position of the syntactical first token, call the
     * corresponding method of <CODE>getFirstElement()</CODE>.
     *
     * @return the relative position of the primary token.
     */
    public recoder.java.SourceElement.Position getRelativePosition() {
        return posInfo.getRelativePosition();
    }


    public PositionInfo getPositionInfo() {
        return posInfo;
    }



    /** toString */
    public String toString() {
        PrettyPrinter pp = PrettyPrinter.purePrinter();
        pp.print(this);
        return pp.result();
    }

    /**
     * this violates immutability, but the method is only called right after the object is
     * created...
     *
     * @param s the path of the parent class as String
     */
    protected void setParentClass(URI s) {
        posInfo.setParentClassURI(s);
    }

    /** get the class the statement originates from */
    public URI getParentClass() {
        return posInfo.getParentClassURI();
    }

}
