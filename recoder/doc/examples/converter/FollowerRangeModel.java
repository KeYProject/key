/*
 * 1.1+Swing version.
 */

import javax.swing.*;
import javax.swing.event.*;

public class FollowerRangeModel extends ConverterRangeModel
                                implements ChangeListener {
    ConverterRangeModel dataModel;

    public FollowerRangeModel(ConverterRangeModel dataModel) {
        this.dataModel = dataModel;
        dataModel.addChangeListener(this);
    }

    public void stateChanged(ChangeEvent e) {
        fireStateChanged();
    }

    public int getMaximum() {
        int modelMax = dataModel.getMaximum();
        double multiplyBy = dataModel.getMultiplier()/multiplier;
        if (DEBUG) {
            System.out.println("In FollowerRangeModel getMaximum");
            System.out.println("  dataModel.getMaximum = " + modelMax
                                + "; multiply by " + multiplyBy
                                + "; result: " + modelMax*multiplyBy);
        }
        return (int)(modelMax * multiplyBy);
    }

    public void setMaximum(int newMaximum) {
        dataModel.setMaximum((int)(newMaximum * 
                     (multiplier/dataModel.getMultiplier())));
    }

    public int getValue() {
        return (int)getDoubleValue();
    }

    public void setValue(int newValue) {
        setDoubleValue((double)newValue);
    }

    public double getDoubleValue() {
        return dataModel.getDoubleValue()
               * dataModel.getMultiplier()
               / multiplier;
    }

    public void setDoubleValue(double newValue) {
        dataModel.setDoubleValue(
                     newValue * multiplier
                     / dataModel.getMultiplier());
    }

    public int getExtent() {
        return super.getExtent();
    }

    public void setExtent(int newExtent) {
        super.setExtent(newExtent);
    }

    public void setRangeProperties(int value,
                                   int extent,
                                   int min,
                                   int max,
                                   boolean adjusting) {
        double multiplyBy = multiplier/dataModel.getMultiplier();
        dataModel.setRangeProperties(value*multiplyBy,
                                     extent, min, 
                                     (int)(max*multiplyBy),
                                     adjusting);
    }
}
