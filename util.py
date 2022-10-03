import os

TEMP_FILE_NAME = "tmp"
TEMP_FILE_DIR = "tmp/"

LOG_FILE_DIR = "log/"


def path_to_filename(path):
    basename = os.path.basename(path)
    filename, extension = os.path.splitext(basename)

    return filename

def get_tmp_filename(infile, outfile):
    infile_path = infile.name
        
    if infile_path != '<stdin>':
        return path_to_filename(infile_path)
        
    return TEMP_FILE_NAME

def write_tempfile(self, path, code):
    if not os.path.isdir(TEMP_FILE_DIR):
        os.mkdir(TEMP_FILE_DIR)

    with open(path, 'w') as f:
        f.write(code)