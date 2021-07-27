package org.key_project.ui.interactionlog.model;

import org.key_project.ui.interactionlog.api.Interaction;

public interface InteractionRecorderListener {
    public void onInteraction(Interaction event);
}
