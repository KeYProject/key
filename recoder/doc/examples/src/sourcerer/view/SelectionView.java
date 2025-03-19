package sourcerer.view;

import sourcerer.SelectionModel;

public interface SelectionView {

    SelectionModel getModel();
    void setModel(SelectionModel model);
    void modelUpdated(boolean selectionRemoved);
}
