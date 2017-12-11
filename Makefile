SHELL := /bin/bash
IMAGE_VERSION=2017-12-10
IMAGE_NAME="vakaras/prusti:${IMAGE_VERSION}"

build_image:
	sudo docker build -t ${IMAGE_NAME} docker
