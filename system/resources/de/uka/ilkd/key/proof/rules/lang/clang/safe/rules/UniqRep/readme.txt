These rules work only in unique integer representation model.
I.e. T::toInt-1(i) is uniquely defined. Arithmetic overflows 
lead to undefined behavior. We also assume
	isValidVal(T::fromInt(i)) <--> T::inIntegerRange(i)

