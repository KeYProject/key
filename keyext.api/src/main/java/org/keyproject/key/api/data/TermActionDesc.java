package org.keyproject.key.api.data;

import org.keyproject.key.api.data.KeyIdentifications.TermActionId;

/**
 * @author Alexander Weigl
 * @version 1 (13.10.23)
 */
public record TermActionDesc(TermActionId commandId, String displayName, String description, String category,
                             TermActionKind kind) {
}
