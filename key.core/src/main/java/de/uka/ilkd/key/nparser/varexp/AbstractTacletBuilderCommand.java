/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.nparser.varexp;


/**
 * Simple default implementation for {@link TacletBuilderCommand}.
 *
 * @author Alexander Weigl
 * @version 1 (12/9/19)
 */
public abstract class AbstractTacletBuilderCommand implements TacletBuilderCommand {
    protected final TacletBuilderCommandInfo info;

    protected AbstractTacletBuilderCommand(TacletBuilderCommandInfo info) {
        this.info = info;
    }

    @Override
    public boolean isSuitableFor(String name) {
        if (info.name().equalsIgnoreCase(name)) {
            return true;
        }
        // handling leading backslashes
        if (name.startsWith("\\")) {
            return isSuitableFor(name.substring(1));
        }
        return false;
    }

    @Override
    public TacletBuilderCommandInfo getInformation() {
        return info;
    }
}
