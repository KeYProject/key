/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.java.ast;


import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/// Exclude a field from equality and hashCode.
@Retention(RetentionPolicy.SOURCE)
@Target({ ElementType.PARAMETER, ElementType.FIELD })
public @interface EqEx {
}
