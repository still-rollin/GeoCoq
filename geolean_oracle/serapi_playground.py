import subprocess

p = subprocess.Popen(
    ["sertop"],
    stdin=subprocess.PIPE,
    stdout=subprocess.PIPE,
    stderr=subprocess.PIPE,
    text=True,
)

print("started")
