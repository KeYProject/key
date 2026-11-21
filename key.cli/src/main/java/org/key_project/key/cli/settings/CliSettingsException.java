/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli.settings;

/**
 * Signals an invalid {@code --settings-file}: an unknown §5.2 key or a value that is not one of
 * the documented alternatives. The message carries the exact offending source line so the CLI can
 * report it verbatim.
 *
 * @see SettingsFileParser
 */
public final class CliSettingsException extends RuntimeException {

    CliSettingsException(String message) {
        super(message);
    }
}
