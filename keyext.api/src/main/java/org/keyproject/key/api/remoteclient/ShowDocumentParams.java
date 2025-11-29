/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.remoteclient;

import org.jspecify.annotations.Nullable;
import org.keyproject.key.api.data.TextRange;

/**
 * Information to show a document on the client side.
 *
 * @param uri The uri to show.
 * @param external Indicates to show the resource in an external program.
 *        To show, for example, `https://code.visualstudio.com/`
 *        in the default WEB browser set `external` to `true`.
 * @param takeFocus An optional property to indicate whether the editor
 *        showing the document should take focus or not.
 *        Clients might ignore this property if an external
 *        program is started.
 * @param selection An optional selection range if the document is a text
 *        document. Clients might ignore the property if an
 *        external program is started or the file is not a text
 *        file.
 */
public record ShowDocumentParams(
        String uri,
        boolean external,
        boolean takeFocus,
        @Nullable TextRange selection) {
}
