package model.url;

public class BlobAbsoluteUrl extends Url {
	
	public Domain domain;
	
	public BlobAbsoluteUrl(String name) {
		super(name);
		this.scheme = Scheme.Blob;
		this.corresponding = "blob://example.com";
		this.correspondingOrigin = "BlankOrigin";
	}

}
