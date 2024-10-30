/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic;

import org.key_project.logic.Program;
import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.ast.RustyProgramElement;

import org.jspecify.annotations.NonNull;

public record RustyBlock(RustyProgramElement program)implements Program{@Override public @NonNull SyntaxElement getChild(int n){if(n==0)return program;throw new IndexOutOfBoundsException("RustyBlock "+this+" has only one child");}

@Override public int getChildCount(){return 1;}

public boolean isEmpty(){return false;}

@Override public String toString(){return program.toString();}

@Override public boolean equals(Object o){if(o==this)return true;if(!(o instanceof RustyBlock rb))return false;if(rb.program()==null)return program()==null;return rb.program().equals(program());}

/** returns the hashCode */
public int hashCode(){return 17+((program()==null)?0:program().hashCode());}}
