package model.url;

public class DataUrl extends Url {
	
	public DataUrl(String name) {
		super(name);
		this.scheme = Scheme.Data;
		this.corresponding = "data:text/plain;charset=utf-8,Hello";
		this.correspondingOrigin = "OpaqueOrigin";
	}

}
