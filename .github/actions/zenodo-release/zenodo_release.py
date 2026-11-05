#!/usr/bin/env python3
"""
Zenodo release automation script.
Handles creating new versions, uploading files, and publishing to Zenodo.
"""

import argparse
import json
import os
import sys
from datetime import date
from pathlib import Path
from typing import Optional, Dict, Any

import requests


def _title(deposition: Dict[str, Any]) -> Optional[str]:
    return deposition.get('metadata', {}).get('title', deposition.get('title'))


class ZenodoReleaser:
    def __init__(self, token: str, record_id: Optional[str] = None):
        self.token = token
        self.record_id = record_id
        self.base_url = "https://zenodo.org/api"
        self.headers = {
            "Authorization": f"Bearer {token}",
            "Content-Type": "application/json"
        }

    def _make_request(self, method: str, url: str, **kwargs) -> requests.Response:
        """Make HTTP request with error handling."""
        try:
            response = requests.request(method, url, **kwargs)
            response.raise_for_status()
            return response
        except requests.exceptions.RequestException as e:
            print(f"Request failed: {e}")
            if hasattr(e.response, 'text'):
                print(f"Response: {e.response.text}")
            raise

    def get_record_info(self) -> Dict[str, Any]:
        """Get information about the record."""
        url = f"{self.base_url}/records/{self.record_id}"
        response = self._make_request("GET", url)
        return response.json()

    def get_draft_depositions(self) -> list:
        """Get all draft depositions for this record."""
        # First, resolve the concept record ID from the record info
        record_info = self.get_record_info()
        concept_recid = record_info.get('conceptrecid', self.record_id)
        
        url = f"{self.base_url}/deposit/depositions"
        params = {"q": f"conceptrecid:{concept_recid}", "all_versions": "true"}
        response = self._make_request("GET", url, headers=self.headers, params=params)
        data = response.json()
        
        # Filter for drafts only
        drafts = [d for d in data if d.get('submitted') is False]
        return drafts

    def delete_draft(self, deposition_id: str) -> None:
        """Delete a draft deposition."""
        url = f"{self.base_url}/deposit/depositions/{deposition_id}"
        print(f"Deleting draft deposition {deposition_id}...")
        try:
            self._make_request("DELETE", url, headers=self.headers)
            print(f"Successfully deleted draft {deposition_id}")
        except Exception as e:
            print(f"Warning: Could not delete draft {deposition_id}: {e}")

    def cleanup_existing_drafts(self) -> None:
        """Clean up any existing draft versions that might be in limbo."""
        print("Checking for existing draft versions...")
        drafts = self.get_draft_depositions()
        
        if drafts:
            print(f"Found {len(drafts)} existing draft(s). Cleaning up...")
            for draft in drafts:
                draft_id = draft['id']
                self.delete_draft(draft_id)
        else:
            print("No existing drafts found.")

    def create_new_version(self) -> Dict[str, Any]:
        """Create a new version of the record, reusing an existing draft if one exists."""
        print(f"Creating new version for record {self.record_id}")
        
        url = f"{self.base_url}/deposit/depositions/{self.record_id}/actions/newversion"
        try:
            response = self._make_request("POST", url, headers=self.headers)
            data = response.json()
        except requests.exceptions.HTTPError as e:
            if e.response is not None and e.response.status_code == 400:
                print("New version draft already exists, retrieving it...")
                return self._get_existing_draft()
            raise
        
        # Get the latest draft URL from the response
        latest_draft_url = data.get('links', {}).get('latest_draft')
        if not latest_draft_url:
            raise ValueError("Could not get latest draft URL from response")
        
        # Fetch the draft to get the actual deposition data
        draft_response = self._make_request("GET", latest_draft_url, headers=self.headers)
        draft_data = draft_response.json()
        
        return draft_data

    def find_record_by_title(self, title: str) -> Optional[str]:
        """Find the latest published deposition of this account with exactly the given title."""
        url = f"{self.base_url}/deposit/depositions"
        params = {"q": f'title:"{title}"', "all_versions": "true", "size": 100}
        response = self._make_request("GET", url, headers=self.headers, params=params)
        matches = [d for d in response.json()
                   if d.get('submitted') and _title(d) == title]
        if not matches:
            return None
        return str(max(matches, key=lambda d: d['id'])['id'])

    def cleanup_unpublished_records(self, title: str) -> None:
        """Delete never-published depositions with this title, left behind by a failed first release."""
        url = f"{self.base_url}/deposit/depositions"
        params = {"q": f'title:"{title}"', "status": "draft", "size": 100}
        response = self._make_request("GET", url, headers=self.headers, params=params)
        for draft in response.json():
            if draft.get('submitted') is False and _title(draft) == title:
                self.delete_draft(draft['id'])

    def create_new_record(self) -> Dict[str, Any]:
        """Create a brand-new deposition, starting a new concept record."""
        print("Creating new record")
        url = f"{self.base_url}/deposit/depositions"
        response = self._make_request("POST", url, headers=self.headers, json={})
        return response.json()

    def _get_existing_draft(self) -> Dict[str, Any]:
        """Retrieve an existing draft version and clear its files."""
        drafts = self.get_draft_depositions()
        if not drafts:
            raise ValueError(
                "Zenodo reports an existing draft but none could be found via the API. "
                "Please check the Zenodo web UI for stuck drafts."
            )
        
        draft = drafts[0]
        print(f"Found existing draft {draft['id']}, cleaning up its files...")
        self.delete_existing_files(draft)
        
        # Re-fetch the draft to get updated state
        url = f"{self.base_url}/deposit/depositions/{draft['id']}"
        response = self._make_request("GET", url, headers=self.headers)
        return response.json()

    def update_metadata(self, deposition_data: Dict[str, Any], tool_name: str, metadata_file: Path) -> None:
        """Update the metadata for the deposition."""
        deposition_id = deposition_data['id']
        print(f"Updating metadata for deposition {deposition_id}")
        
        today = date.today().strftime('%Y-%m-%d')
        metadata = load_metadata(metadata_file, tool_name, today)
        
        # Update the deposition
        url = deposition_data['links']['self']
        response = self._make_request("PUT", url, headers=self.headers, json=metadata)
        
        print(f"Metadata updated successfully (date := {today}, tool := {tool_name})")
        return response.json()

    def delete_existing_files(self, deposition_data: Dict[str, Any]) -> None:
        """Delete any existing files from the draft."""
        files = deposition_data.get('files', [])
        if not files:
            print("No existing files to delete.")
            return
        
        print(f"Deleting {len(files)} existing file(s)...")
        for file_info in files:
            file_id = file_info['id']
            deposition_id = deposition_data['id']
            url = f"{self.base_url}/deposit/depositions/{deposition_id}/files/{file_id}"
            try:
                self._make_request("DELETE", url, headers=self.headers)
                print(f"Deleted file: {file_info['filename']}")
            except Exception as e:
                print(f"Warning: Could not delete file {file_info['filename']}: {e}")

    def upload_file(self, deposition_data: Dict[str, Any], file_path: Path) -> None:
        """Upload a file to the deposition."""
        bucket_url = deposition_data['links']['bucket']
        filename = file_path.name
        
        print(f"Uploading file: {filename} ({file_path.stat().st_size / (1024*1024):.2f} MB)")
        
        # Upload using the bucket API (streaming)
        upload_url = f"{bucket_url}/{filename}"
        with open(file_path, 'rb') as f:
            headers = {"Authorization": f"Bearer {self.token}"}
            response = self._make_request("PUT", upload_url, headers=headers, data=f)
        
        print(f"Upload successful: {filename}")

    def publish(self, deposition_data: Dict[str, Any]) -> Dict[str, Any]:
        """Publish the deposition."""
        publish_url = deposition_data['links']['publish']
        print(f"Publishing deposition...")
        
        response = self._make_request("POST", publish_url, headers=self.headers)
        data = response.json()
        
        doi = data.get('doi', 'N/A')
        doi_url = data.get('doi_url', 'N/A')
        print(f"Publish successful!")
        print(f"DOI: {doi}")
        print(f"DOI URL: {doi_url}")
        
        return data


def load_metadata(metadata_file: Path, tool_name: str, today: str) -> Dict[str, Any]:
    """Read the metadata template and fill in its placeholders."""
    with open(metadata_file, 'r') as f:
        metadata_json = json.dumps(json.load(f))
    metadata_json = metadata_json.replace('__TODAY__', today)
    metadata_json = metadata_json.replace('__TOOL__', tool_name)
    return json.loads(metadata_json)


def main():
    parser = argparse.ArgumentParser(description='Create and publish a Zenodo release')
    parser.add_argument('--token', required=True, help='Zenodo API token')
    parser.add_argument('--record-id', default='',
                       help='Previous record ID; if omitted, the record is looked up by title '
                            'and created on first release')
    parser.add_argument('--tool', required=True, help='Tool name')
    parser.add_argument('--file', required=True, help='ZIP file to upload')
    parser.add_argument('--metadata', required=True, help='Metadata JSON file')
    parser.add_argument('--cleanup-drafts', action='store_true', 
                       help='Clean up existing draft versions before creating new one')
    
    args = parser.parse_args()
    
    # Validate file paths
    file_path = Path(args.file)
    if not file_path.exists():
        print(f"Error: File not found: {file_path}")
        sys.exit(1)
    
    metadata_path = Path(args.metadata)
    if not metadata_path.exists():
        print(f"Error: Metadata file not found: {metadata_path}")
        sys.exit(1)
    
    try:
        releaser = ZenodoReleaser(args.token, args.record_id or None)
        
        # Without an explicit record, the title identifies the tool's record, so the first
        # release creates it and later ones find it again.
        if not releaser.record_id:
            title = load_metadata(metadata_path, args.tool, '')['metadata']['title']
            releaser.record_id = releaser.find_record_by_title(title)
            if releaser.record_id:
                print(f"Found existing record {releaser.record_id} titled '{title}'")
        
        if releaser.record_id:
            # Optional: Clean up any existing drafts
            if args.cleanup_drafts:
                releaser.cleanup_existing_drafts()
            
            # Create new version
            deposition = releaser.create_new_version()
        else:
            if args.cleanup_drafts:
                releaser.cleanup_unpublished_records(title)
            deposition = releaser.create_new_record()
        
        # Update metadata
        deposition = releaser.update_metadata(deposition, args.tool, metadata_path)
        
        # Delete any existing files from the draft
        releaser.delete_existing_files(deposition)
        
        # Upload the file
        releaser.upload_file(deposition, file_path)
        
        # Publish
        releaser.publish(deposition)
        
        print("\n=== Release completed successfully! ===")
        
    except Exception as e:
        print(f"\n=== Release failed ===")
        print(f"Error: {e}")
        sys.exit(1)


if __name__ == '__main__':
    main()
