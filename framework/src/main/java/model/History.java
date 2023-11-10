package model;

import org.javers.core.metamodel.annotation.Id;

import model.url.Url;

public class History {
	
	
	@Id
	public String name;
	
	public Url url;
	
	
	public History(String _name) {
		this.name = _name;
	}


}
