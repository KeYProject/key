/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.jml.pretranslation;

import de.uka.ilkd.key.speclang.njml.LabeledParserRuleContext;

/**
 * @author Alexander Weigl
 * @version 1 (03.02.24)
 */
public record JmlAbbreviationEntry(LabeledParserRuleContext first, LabeledParserRuleContext second, LabeledParserRuleContext third) {
}
