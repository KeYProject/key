package org.key_project.key4eclipse.resources.marker;

import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.preference.PreferenceManager;
import org.eclipse.swt.graphics.Image;
import org.key_project.key4eclipse.common.ui.counterExample.SMTPreferenceDialog;
import org.key_project.key4eclipse.common.ui.util.KeYImages;
import org.key_project.key4eclipse.resources.counterexamples.KeYProjectCounterExample;
import org.key_project.key4eclipse.resources.counterexamples.KeYProjectCounterExamplePreferenceNode;
import org.key_project.key4eclipse.resources.io.ProofMetaFileReader;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;
import org.key_project.util.eclipse.WorkbenchUtil;

public class ShowCounterExamplesResolution extends AbstractProofMarkerResolution {

    public ShowCounterExamplesResolution(IMarker marker) throws CoreException {
        super(marker);
    }

    @Override
    public Image getImage() {
        return KeYImages.getImage(KeYImages.KEY_LOGO);
    }

    @Override
    protected String getClosedMarkerDescriptionPrefix() {
        return "A closed proof can not have any counter examples!";
    }

    @Override
    protected String getNotClosedMarkerDescriptionPrefix() {
        return "Shows all available counter examples for: ";
    }

    @Override
    protected String getLabelPrefix() {
        return "Show Counter Examples: ";
    }

    @Override
    protected void run(IMarker marker, IFile proofFile) throws Exception {
        IFile metaFile = KeYResourcesUtil.getProofMetaFile(proofFile);
        ProofMetaFileReader pmfr = new ProofMetaFileReader(metaFile);
        
        List<KeYProjectCounterExample> counterExamples = pmfr.getCounterExamples();
        if(counterExamples.isEmpty())
            return;
        PreferenceManager manager = new PreferenceManager();
        SMTPreferenceDialog dialog = new SMTPreferenceDialog(WorkbenchUtil.getActiveShell(), manager);
        for (KeYProjectCounterExample ce : counterExamples) {
            manager.addToRoot(new KeYProjectCounterExamplePreferenceNode(ce, null));
        }
        dialog.open();
    }

}
