package hu.bme.mit.inf.ttmc.code.util;

import java.util.HashMap;
import java.util.NoSuchElementException;

public class SymbolTable<Node> {
	
	private class SymbolTableScope<Node> {

		private HashMap<String, Node> nodes = new HashMap<String, Node>();

		private SymbolTableScope<Node> parent;
		
		public boolean contains(String name)
		{
			boolean has = false;
			if (has = nodes.containsKey(name)) {
				return true;
			}
			
			if (parent == null)
				return false;
			
			return parent.contains(name);
		}
		
		public boolean currentContains(String name)
		{
			return nodes.containsKey(name);
		}
		
		public Node get(String name)
		{
			Node elem;
			if ((elem = nodes.get(name)) != null)
				return elem;
			
			if (parent == null)
				throw new NoSuchElementException();
			
			return parent.get(name);
		}
		
		public void put(String name, Node node)
		{
			nodes.put(name, node);
		}
	}
	
	private SymbolTableScope<Node> top;

	public SymbolTable() {
		this.top = new SymbolTableScope<Node>();
	}
	
	public boolean contains(String name)
	{
		return top.contains(name);
	}
	
	public boolean currentScopeContains(String name)
	{
		return top.currentContains(name);
	}
	
	public Node get(String name)
	{
		return top.get(name);
	}
	
	public void put(String name, Node node)
	{
		top.put(name, node);
	}
	
	public void pushScope()
	{
		SymbolTableScope<Node> scope = new SymbolTableScope<>();
		scope.parent = top;
		
		top = scope;
	}
	
	public void popScope()
	{
		top = top.parent;
	}
		
}
