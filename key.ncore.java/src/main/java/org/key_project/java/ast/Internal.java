/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.java.ast;

/**
 * This annotation marks fields and methods that are added for internal purposes,
 * and should not be exposed.
 * It is used in the code generation to avoid processing of fields or methods.
 *
 * @author Alexander Weigl
 * @version 1 (17.05.26)
 */
public @interface Internal {
}
