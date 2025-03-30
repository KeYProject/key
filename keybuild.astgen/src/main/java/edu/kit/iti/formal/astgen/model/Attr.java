/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package edu.kit.iti.formal.astgen.model;

import com.palantir.javapoet.TypeName;
import org.jspecify.annotations.Nullable;


/**
 * @author Alexander Weigl
 * @version 1 (10.09.17)
 */
public record Attr(String name, TypeName type,
        boolean nullable,
        boolean isMulti,
        @Nullable String comment) {
}
