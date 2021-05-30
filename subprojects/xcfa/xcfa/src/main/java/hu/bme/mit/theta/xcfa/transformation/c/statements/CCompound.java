package hu.bme.mit.theta.xcfa.transformation.c.statements;

import java.util.ArrayList;
import java.util.List;

public class CCompound extends CStatement{
	private final List<CStatement> cStatementList;

	public CCompound() {
		cStatementList = new ArrayList<>();
	}

	public List<CStatement> getcStatementList() {
		return cStatementList;
	}
}
