package org.key_project.key4eclipse.resources.counterexamples;

import org.eclipse.jface.preference.PreferenceNode;
import org.eclipse.jface.resource.ImageDescriptor;


public class KeYProjectCounterExamplePreferenceNode extends PreferenceNode {
    
    private KeYProjectCounterExampleModel model;

    public KeYProjectCounterExamplePreferenceNode(
                                    KeYProjectCounterExample ce,
                                    ImageDescriptor image) {
       super(ce.getProblemId(), ce.getProblemName(), image, null);
       this.model = ce.getModel();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void createPage() {
       KeYProjectCounterExamplePropertyPage page = new KeYProjectCounterExamplePropertyPage(model);
       if (getLabelImage() != null) {
          page.setImageDescriptor(getImageDescriptor());
       }
       page.setTitle(getLabelText());
       setPage(page);
    }
 }
