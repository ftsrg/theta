package hu.bme.mit.inf.ttmc.constraint.ui;

import java.io.IOException;
import java.util.Collections;

import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.xtext.resource.XtextResource;
import org.eclipse.xtext.resource.XtextResourceSet;

import com.google.inject.Inject;
import com.google.inject.Injector;

import hu.bme.mit.inf.ttmc.constraint.language.ConstraintLanguageStandaloneSetup;
import hu.bme.mit.inf.ttmc.constraint.model.ConstraintModelPackage;
import hu.bme.mit.inf.ttmc.constraint.model.ConstraintSpecification;


public class ConstraintModelLoader {

	private static ConstraintModelLoader instance;

	@Inject
	private XtextResourceSet resourceSet;

	private ConstraintModelLoader() {
		final ConstraintLanguageStandaloneSetup setup = new ConstraintLanguageStandaloneSetup();
		final Injector injector = setup.createInjectorAndDoEMFRegistration();
		ConstraintModelPackage.eINSTANCE.eClass();
		injector.injectMembers(this);
		resourceSet.addLoadOption(XtextResource.OPTION_RESOLVE_ALL, Boolean.TRUE);
	}

	public static ConstraintModelLoader getInstance() {
		if (instance == null) {
			instance = new ConstraintModelLoader();
		}
		return instance;
	}

	public ConstraintSpecification load(String fileName) {
		final URI uri = URI.createFileURI(fileName);
		final Resource resource = resourceSet.getResource(uri, true);
		final EObject object = resource.getContents().get(0);
		final ConstraintSpecification specification = (ConstraintSpecification) object;
		return specification;
	}

	public void save(ConstraintSpecification specification, String fileName) throws IOException {
		final URI uri = URI.createFileURI(fileName);
		final Resource resource = resourceSet.createResource(uri);
		resource.getContents().add(specification);
       	resource.save(Collections.EMPTY_MAP);
    }
}
