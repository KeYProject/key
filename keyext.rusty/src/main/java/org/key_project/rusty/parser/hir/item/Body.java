/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser.hir.item;

import java.util.Arrays;

import org.key_project.rusty.parser.hir.expr.Expr;

public record Body(Param[]params,Expr value){@Override public String toString(){return"Body{"+"params="+Arrays.toString(params)+", value="+value+'}';}}
