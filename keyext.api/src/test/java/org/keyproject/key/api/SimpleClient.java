/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api;

import java.util.concurrent.CompletableFuture;
import javax.annotation.Nullable;

import org.jspecify.annotations.NullMarked;
import org.keyproject.key.api.data.TaskFinishedInfo;
import org.keyproject.key.api.data.TaskStartedInfo;
import org.keyproject.key.api.remoteclient.*;

@NullMarked
class SimpleClient implements ClientApi {

    @Override
    public void logTrace(LogTraceParams params) {

    }

    @Override
    public void showMessage(ShowMessageParams params) {

    }

    @Nullable
    @Override
    public CompletableFuture<MessageActionItem> showMessageWithActions(
            ShowMessageRequestParams params) {
        return null;
    }

    @Override
    public CompletableFuture<ShowDocumentResult> showDocument(ShowDocumentParams params) {
        return null;
    }

    @Override
    public void taskFinished(TaskFinishedInfo info) {
        System.out.println(info);
    }

    @Override
    public void taskProgress(int position) {

    }

    @Override
    public void taskStarted(TaskStartedInfo info) {
        System.out.println(info);
    }
}
