class VarArg {

    public Object varArg(int fix, Object[]... var) {
	if(fix > 0)
	    return var[fix];
	else
	    return null;
    }

}
